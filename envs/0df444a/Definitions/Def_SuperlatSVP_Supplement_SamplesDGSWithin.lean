-- Prove2me | Definitions.Def_SuperlatSVP_Supplement_SamplesDGSWithin
-- name    : SuperlatSVP_Supplement_SamplesDGSWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:35:56.589573+00:00
-- url     : https://prove2.me/theorems/799a1c13-8b9c-4797-a85c-8f40795a340d
-- title:
--   A randomized program samples within total variation $\delta$ of the discrete Gaussian $D_{L(B),s}$
-- statement:
--   For $s>0$ let $\rho_s(x)=e^{-\pi\|x\|^2/s^2}$ on $\mathbb R^n$, and for a full-rank lattice $L$ let $\rho_s(L)=\sum_{y\in L}\rho_s(y)$. The **discrete Gaussian** $D_{L,s}$ is the probability distribution on $L$ with
--   $$D_{L,s}(x)=\frac{\rho_s(x)}{\rho_s(L)}\qquad(x\in L).$$
--   The **total variation distance** of two probability distributions $P,Q$ on a set is $d_{TV}(P,Q)=\sup_A|P(A)-Q(A)|$.
--
--   A sampling instance is an invertible $B\in\mathbb Q^{n\times n}$, a rational width parameter $a$ and a rational accuracy parameter $\kappa$. Its input word is $n$, the entries of $B$ row by row, then $a$, then $\kappa$, and $\ell$ is its total bit length. A sampler outputs a lattice point $Bx$ of $L(B)$ by writing its integer coefficient vector $x\in\mathbb Z^n$.
--
--   A program $P$ on the published randomized RAM `TwMSOCount.Main` **samples within total variation $\delta$ of $D_{L(B),s}$** on a word $w$ when:
--
--   1. for every possible output, the event that $P$ produces it is measurable;
--   2. for every set $A$ of possible outputs (including malformed words and "no output"), the probability that the output lies in $A$ differs by at most $\delta$ from the probability that the coefficient word of a sample of $D_{L(B),s}$ lies in $A$.
--
--   The module also defines the input word, the bit length $\ell$, and the predicate "halts on every coin tape within bit time $T$ and bit space $S$". Theorems 1.9 and 3.4 use all of these.
--
--   **Formalization Note** The distance is taken over all possible outputs, so an output that is not the coefficient word of a lattice point counts fully as error. The Gaussian mass $\rho_s(L)$ is the published `SuperlatSVP.rhoSet`, a sum in $[0,\infty]$.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §2.2, p.16 (ρ_s, D_{A,s}); §2.4, p.20 (d_TV); Theorem 3.4, p.25; Algorithm 6, p.55; Theorem 1.9, pp.6, 57

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_SolvesSVPWithin

open MeasureTheory TwMSOCount.Main
open scoped ENNReal

namespace SuperlatSVP.Supplement

/-- The bit length of a word of stored rationals: the sum of their bit lengths. -/
def wordBits (w : List ℚ) : ℕ := (w.map qbits).sum

/-- The input word of a sampling instance: `n`, the entries of `B` row by row, then the width
parameter `a` (the width `s` in Theorem 3.4, the squared width `s²` in Theorem 1.9), then the
accuracy parameter `κ`. -/
def dgsInput {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (a κ : ℚ) : List ℚ :=
  encBasis B ++ [a, κ]

/-- The run of `P` on the word `w` halts on **every** coin tape, with bit time at most `T` and bit
space at most `S`. -/
def HaltsWithin (P : Program) (w : List ℚ) (T S : ℝ) : Prop :=
  ∀ τ : ℕ → Bool, ∃ s : RunStats, runStats P τ (Config.init w) = some s ∧
    (s.time : ℝ) ≤ T ∧ (s.space : ℝ) ≤ S

/-- The lattice point `Bx ∈ L(B)` of a coefficient vector `x ∈ ℤⁿ`, as a point of `ℝⁿ`. -/
noncomputable def coeffPoint {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℤ) : E n :=
  vecE (fun i => ((B.mulVec (fun j => (x j : ℚ))) i : ℝ))

/-- The discrete Gaussian `D_{L(B),s}` (§2.2, p.16: `D_{A,s}(x) = ρ_s(x)/ρ_s(A)`,
`ρ_s(x) = e^{−π‖x‖²/s²}`), transported to coefficient vectors: the mass of `x ∈ ℤⁿ` is
`ρ_s(Bx)/ρ_s(L(B))`. -/
noncomputable def dgsCoeffMass {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (s : ℝ) (x : Fin n → ℤ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (RegevLWE.GaussConv.rho s (coeffPoint B x)) /
    rhoSet s (lat (B.map (fun q : ℚ => (q : ℝ))) : Set (E n))

/-- The probability, under fair coins, that the output of `P` on the word `w` lies in the set `A`
of possible outputs (`none` = no halt). -/
noncomputable def outProb (P : Program) (w : List ℚ) (A : Set (Option (List ℚ))) : ℝ≥0∞ :=
  coinTape {τ | callOutput P (Config.init w) τ ∈ A}

/-- The probability of the set `A` of output words under the ideal answer: the output word
`encIntVec x` of a coefficient vector `x` drawn from `D_{L(B),s}`. -/
noncomputable def dgsProb {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (s : ℝ)
    (A : Set (Option (List ℚ))) : ℝ≥0∞ :=
  ∑' x : Fin n → ℤ, ({x | some (encIntVec x) ∈ A} : Set (Fin n → ℤ)).indicator
    (dgsCoeffMass B s) x

/-- The output of `P` on the word `w` is within total variation `δ` of `D_{L(B),s}`. Hhan, Kim,
Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete Gaussian
sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §2.4, p.20 (PDF p.20):
"total variation distance is dTV(P, Q) = supA |P(A) − Q(A)|"; Theorem 3.4, p.25 and Theorem 1.9,
pp.6, 57 ("outputs a point x ∈ L within total variation … of DL,s").

1. for every possible output `o`, the event that the output is `o` is measurable;
2. for every set `A` of possible outputs, `|Pr[output ∈ A] − D_{L(B),s}(A)| ≤ δ`.

**Formalization Note.** The output is the integer coefficient vector `x` of the lattice point
`Bx`, written as the word `encIntVec x` (as in the published `SuperlatSVP.svpSuccess`). The total
variation is taken over **all** possible outputs (`Option (List ℚ)`): a malformed word, a word of
the wrong length and a non-halting run carry no ideal mass, so they count fully toward the
distance. Masses are in `ℝ≥0∞`; `ρ_s(L(B))` is the published `SuperlatSVP.rhoSet` (finite and
positive for an invertible `B` and `s > 0`). -/
def SamplesDGSWithin (P : Program) (w : List ℚ) {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ)
    (s δ : ℝ) : Prop :=
  (∀ o : Option (List ℚ), MeasurableSet {τ | callOutput P (Config.init w) τ = o}) ∧
    ∀ A : Set (Option (List ℚ)), |(outProb P w A).toReal - (dgsProb B s A).toReal| ≤ δ

end SuperlatSVP.Supplement


