-- Prove2me | Definitions.Def_AcceptSubcube_Supplement_RP
-- name    : AcceptSubcube_Supplement_RP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:48:16.430216+00:00
-- url     : https://prove2.me/theorems/0d40b86a-8691-4cac-832f-0b2293537bc5
-- title:
--   The classes $\mathsf{RP}$ and $\mathsf{BPP}$, and the statements $\mathsf{NP}\subseteq\mathsf{BPP}$, $\mathsf{NP}=\mathsf{RP}$, $\mathsf P=\mathsf{NP}$
-- statement:
--   A language $L$ over a finite alphabet $\Sigma$ is in $\mathsf{RP}$ if there are a relation $R(w,r)$ between inputs $w\in\Sigma^*$ and coin strings $r\in\{0,1\}^*$, decidable in polynomial time, and an integer $k$ such that, with coin strings of length $|w|^k+k$ drawn uniformly,
--
--   1. if $w\in L$, then $R(w,r)$ holds for at least half of the coin strings;
--   2. if $w\notin L$, then $R(w,r)$ holds for no coin string.
--
--   $L$ is in $\mathsf{BPP}$ if the same holds with acceptance probability at least $2/3$ for members and at most $1/3$ for non-members.
--
--   The statements $\mathsf{NP}\subseteq\mathsf{BPP}$, $\mathsf{NP}=\mathsf{RP}$ and $\mathsf P=\mathsf{NP}$ are asserted for languages over every finite alphabet.
--
--   These are the conclusions of the hardness theorems of the paper (Theorems 1.2, 5.7, 7.9): an approximation algorithm for complete Min-CSPs would place an $\mathsf{NP}$-hard problem in one of these classes.
--
--   **Formalization Note** "Decidable in polynomial time" means that the language $\{w\#r : R(w,r)\}$ is in the published class $\mathsf P$ of Cook's one-tape Turing machines (`CookPvsNP.P`), exactly as the published `CookPvsNP.NP` uses a polynomial-time checking relation. So $\mathsf P$, $\mathsf{NP}$, $\mathsf{RP}$ and $\mathsf{BPP}$ are classes of one machine model, the model over which the published Unique Games Conjecture `OptInapprox.MaxCut.UGC` states its $\mathsf{NP}$-hardness. Probabilities are exact fractions of coin strings.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.2, pp.4–5; Proof of Lemma 7.2, p.36 (RP algorithm); §8.4, p.46 (promise-BPP)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_AcceptSubcube_coinFrac

namespace AcceptSubcube.Supplement

/-- **The class RP** of languages over the finite alphabet `Sym`, on the machine model of the
published `CookPvsNP` (Cook's one-tape Turing machines).

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.2(b), p.5 and Proof of Lemma 7.2,
p.36: "An unsatisfiable input is never accepted, whatever the random bits. A satisfiable input is
accepted with probability … 2/3. This is an RP algorithm".

`L ∈ RP Sym` iff there are a relation `R(w, r)` between inputs and coin strings that is decided in
polynomial time (its language `{w#r}` is in the published `CookPvsNP.P`) and `k` such that, with
coin strings of length `|w|^k + k`: members are accepted for at least half of the coin strings,
non-members for none.

**Formalization Note.** Written in the shape of the published `CookPvsNP.NP` (a polynomial-time
checking relation), with the coin string in place of the certificate and the exact fraction of coin
strings (`coinFrac`) in place of a probability, so that NP, RP, BPP and P are classes of one machine
model and one alphabet convention, the model of the published UGC (`OptInapprox.MaxCut.UGC`). -/
def RP (Sym : Type) [Fintype Sym] : Set (CookPvsNP.Lang Sym) :=
  { L | ∃ (R : List Sym → List Bool → Prop) (k : ℕ),
      CookPvsNP.checkLang R ∈ CookPvsNP.P (Option (Sym ⊕ Bool)) ∧
      ∀ w : List Sym,
        (w ∈ L → (1 : ℝ) / 2 ≤ coinFrac (w.length ^ k + k) (R w)) ∧
        (w ∉ L → ∀ r : List Bool, r.length = w.length ^ k + k → ¬ R w r) }

/-- **The class BPP** (two-sided bounded error), same model as `RP`: members are accepted for at
least `2/3` of the coin strings, non-members for at most `1/3`.

Cai, Jiang, Liu, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.2(a), p.4; §8.4,
p.46 ("places the same NP-hard promise problem in promise-BPP, so NP ⊆ BPP"). -/
def BPP (Sym : Type) [Fintype Sym] : Set (CookPvsNP.Lang Sym) :=
  { L | ∃ (R : List Sym → List Bool → Prop) (k : ℕ),
      CookPvsNP.checkLang R ∈ CookPvsNP.P (Option (Sym ⊕ Bool)) ∧
      ∀ w : List Sym,
        (w ∈ L → (2 : ℝ) / 3 ≤ coinFrac (w.length ^ k + k) (R w)) ∧
        (w ∉ L → coinFrac (w.length ^ k + k) (R w) ≤ (1 : ℝ) / 3) }

/-- `NP ⊆ BPP`, over every finite alphabet (the negation of the paper's assumption `NP ⊄ BPP`). -/
def NPsubBPP : Prop :=
  ∀ (Sym : Type) [Fintype Sym], CookPvsNP.NP Sym ⊆ BPP Sym

/-- `NP = RP`, over every finite alphabet. -/
def NPeqRP : Prop :=
  ∀ (Sym : Type) [Fintype Sym], CookPvsNP.NP Sym = RP Sym

/-- `P = NP`, over every finite alphabet. -/
def PeqNP : Prop :=
  ∀ (Sym : Type) [Fintype Sym], CookPvsNP.P Sym = CookPvsNP.NP Sym

end AcceptSubcube.Supplement


