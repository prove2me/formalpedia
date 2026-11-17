-- Prove2me | Definitions.Def_ProofCryptoSynergy_Supplement_DetHalfLevin
-- name    : ProofCryptoSynergy_Supplement_DetHalfLevin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:46:48.843115+00:00
-- url     : https://prove2.me/theorems/7c1e9279-f980-451c-b82f-c99170512c15
-- title:
--   Deterministic, nonuniform and randomized (half-)Levin reductions from SAT; honesty
-- statement:
--   Reductions from SAT to a learning problem $P$, with time or size bound $t$:
--
--   1. A **deterministic $t$-time half-Levin reduction** is a pair $(f,g)$ of algorithms running in time $t(|x|)$, with $f$ many-one and $g$ mapping witnesses (Definition 4).
--   2. A **nonuniform** half-Levin (resp. Levin) reduction computes $f,g$ (resp. $f,g,h$) by Boolean circuits of size at most $t(|x|)$, one per input length, with $h$ recovering witnesses.
--   3. A **randomized $t$-time half-Levin reduction with $\varepsilon$-error** (Definition 5) has $f(x;r_1)$, $g(x,w;r_1)$ with: for every $(x,w)\in R^{\mathrm{SAT}}_Y$, $\Pr_{r_1}[(f(x;r_1),g(x,w;r_1))\in R^P_Y]\ge1-\varepsilon$; and for every unsatisfiable $x$, $\Pr_{r_1}[f(x;r_1)\in N_P]\ge1-\varepsilon$. The **Levin** version adds $h(x,w';r_1,r_2)$ and requires, with probability $\ge1-\varepsilon$ over $r_1$, also that for every $w'$ with $(f(x;r_1),w')\in R^P_N$, $\Pr_{r_2}[(x,h(x,w';r_1,r_2))\in R^{\mathrm{SAT}}_N]\ge1-\varepsilon$.
--   4. $f$ is **honest** if for some $\delta>0$, $|f(x)|\ge|x|^\delta$ for all $x$.
--   5. For Section 6: $(f,g)$ are deterministic polynomial-time machines, $h$ is a randomized polynomial-time machine, and randomized witness recovery requires $\Pr_r[(x,h(x,w';r))\in R^{\mathrm{SAT}}_N]\ge1-\varepsilon$ whenever $(f(x),w')\in R^P_N$, for all sufficiently long $x$.
--   6. A reduction **outputs instances of polynomial size** (`PolySizeOut`, `RandPolySizeOut`) if for one constant $c$ every output sampler with input length $n$ has a description of length at most $(n+2)^c$ (the learning problems' instances are "poly(n)-size circuits").
--
--   These are the reductions of Theorems 2, 38, 46, 56, 59, 64, 71, 72 and 74.
--
--   **Formalization Note** Machines are the published `KarpLiptonOM.OracleTM` with the empty oracle; outputs are circuit descriptions (`MCircuit.code`, `circCode`). Nonuniform circuits read their arguments through `padIn` and write through `unpadOut`. In Definition 5 condition 1 is printed for $x\in Y_1$ with $w$ free; it is read for every $(x,w)\in R_Y$. $|f(x)|$ is the length of the description of the output sampler.
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definitions 4 and 5, p.17 (PDF 19); Theorems 71, 72, 74, p.53 (PDF 55)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_Supplement_WRel
import Definitions.Def_ProofCryptoSynergy_Supplement_Samp
import Definitions.Def_LaconicBarrier_IOScheme
import Definitions.Def_LaconicBarrier_PolyTimeOn

open KarpLiptonOM LaconicBarrier

namespace ProofCryptoSynergy.Supplement

/-- A **deterministic `t`-time half-Levin reduction** `(f, g)` from SAT to a learning problem `P`
(Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 4, p.17 (PDF 19)): `f` maps formulas to sampling circuits and `g` maps a formula
and a satisfying assignment to a circuit; both are computed by machines within `t(|x|)` steps
(`f` on every `x`, `g` on every `(x, w) ∈ R_Y`); `f` is many-one and `g` maps witnesses.

**Formalization Note** Machines are the published `KarpLiptonOM.OracleTM` with the empty oracle
(`LaconicBarrier.TimeOn`); the output of `f` is the description `MCircuit.code` of the sampling circuit
and that of `g` the description `circCode` of the circuit. -/
def DetHalfLevin (P : WRel Samp Wit) (t : ℕ → ℕ) (f : List Bool → Samp)
    (g : List Bool → List Bool → Wit) : Prop :=
  TimeOn (ι := List Bool) (fun x => [x]) (fun x => (f x).2.code) (fun x => t x.length) ∧
  TimeOn (ι := {i : List Bool × List Bool // SATRel.RY i.1 i.2})
    (fun i => [i.1.1, i.1.2]) (fun i => circCode (g i.1.1 i.1.2).2) (fun i => t i.1.1.length) ∧
  ManyOne SATRel P f ∧ WitnessMap SATRel P f g

/-- A function on the arguments `a` with `|x| = n` (`len a = n`) in the domain `dom` is computed by one
multi-output circuit of size at most `t(n)` per length `n`, reading the encoded argument `enc a` through
`padIn` and writing `out a` through `unpadOut` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 4, p.17: "implemented as boolean
circuits of size at most `t(|x|)`"). -/
def NonuComputes {α : Type} (t : ℕ → ℕ) (len : α → ℕ) (dom : α → Prop) (enc : α → List Bool)
    (out : α → List Bool) : Prop :=
  ∀ n : ℕ, ∃ (k : ℕ) (F : MCircuit k), F.size ≤ t n ∧
    ∀ a, len a = n → dom a → unpadOut (F.eval (padIn k (enc a))) = out a

/-- A **nonuniform `t`-size half-Levin reduction** from SAT to `P` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 4, p.17 (PDF 19)):
as `DetHalfLevin`, with `f` and `g` computed by circuits of size at most `t(|x|)`, one per input length.

**Formalization Note** `g`'s circuit reads `x ++ w`; `|x| = n` is fixed, so the pair is recoverable. -/
def NonuHalfLevin (P : WRel Samp Wit) (t : ℕ → ℕ) (f : List Bool → Samp)
    (g : List Bool → List Bool → Wit) : Prop :=
  NonuComputes t (fun x : List Bool => x.length) (fun _ => True) id (fun x => (f x).2.code) ∧
  NonuComputes (α := List Bool × List Bool) t (fun i => i.1.length) (fun i => SATRel.RY i.1 i.2)
    (fun i => i.1 ++ i.2) (fun i => circCode (g i.1 i.2).2) ∧
  ManyOne SATRel P f ∧ WitnessMap SATRel P f g

/-- A **nonuniform `t`-size Levin reduction** `(f, g, h)` from SAT to `P` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 4, p.17
(PDF 19)): a nonuniform half-Levin reduction together with `h`, computed by circuits of size at most
`t(|x|)` on the pairs `(x, w')` with `(f(x), w') ∈ R_N`, satisfying witness recovery
`(f(x), w') ∈ R₂_N → (x, h(x, w')) ∈ R₁_N`. -/
def NonuLevin (P : WRel Samp Wit) (t : ℕ → ℕ) (f : List Bool → Samp)
    (g : List Bool → List Bool → Wit) (h : List Bool → Wit → List Bool) : Prop :=
  NonuHalfLevin P t f g ∧
  NonuComputes (α := List Bool × Wit) t (fun i => i.1.length) (fun i => P.RN (f i.1) i.2)
    (fun i => i.1 ++ circCode i.2.2) (fun i => h i.1 i.2) ∧
  WitnessRecover SATRel P f h

open Classical in
/-- A **randomized `t`-time half-Levin reduction with `ε`-error** from SAT to `P` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 5,
p.17 (PDF 19)): `f(x; r₁)`, `g(x, w; r₁)` with `ρ(|x|)` shared coins `r₁`, computed by machines within
`t(|x|)` steps, such that
1(a). for every `(x, w) ∈ R₁_Y`, `Pr_{r₁}[(f(x; r₁), g(x, w; r₁)) ∈ R₂_Y] ≥ 1 − ε`;
2. for every `x ∈ N₁`, `Pr_{r₁}[f(x; r₁) ∈ N₂] ≥ 1 − ε`.

**Formalization Note** Condition 1 is printed "for every `x ∈ Y₁`" with `w` free; it is read for every
`(x, w) ∈ R₁_Y`, as the witness mapping of Definition 4. -/
def RandHalfLevin (P : WRel Samp Wit) (t : ℕ → ℕ) (ε : ℝ) (ρ : ℕ → ℕ)
    (f : List Bool → List Bool → Samp) (g : List Bool → List Bool → List Bool → Wit) : Prop :=
  TimeOn (ι := {i : List Bool × List Bool // i.2.length = ρ i.1.length})
    (fun i => [i.1.1, i.1.2]) (fun i => (f i.1.1 i.1.2).2.code) (fun i => t i.1.1.length) ∧
  TimeOn (ι := {i : List Bool × List Bool × List Bool //
      SATRel.RY i.1 i.2.1 ∧ i.2.2.length = ρ i.1.length})
    (fun i => [i.1.1, i.1.2.1, i.1.2.2]) (fun i => circCode (g i.1.1 i.1.2.1 i.1.2.2).2)
    (fun i => t i.1.1.length) ∧
  (∀ x w, SATRel.RY x w → 1 - ε ≤ coinAvg (ρ x.length)
    (fun r => if P.RY (f x (bits r)) (g x w (bits r)) then 1 else 0)) ∧
  (∀ x ∈ SATRel.No, 1 - ε ≤ coinAvg (ρ x.length)
    (fun r => if f x (bits r) ∈ P.No then 1 else 0))

open Classical in
/-- A **randomized `t`-time Levin reduction with `ε`-error** `(f, g, h)` from SAT to `P` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…),
Definition 5, p.17 (PDF 19)): `f(x; r₁)`, `g(x, w; r₁)`, `h(x, w'; r₁, r₂)` with `ρ(|x|)` coins `r₁` and
`ρ₂(|x|)` coins `r₂`, computed by machines within `t(|x|)` steps, such that
1. for every `(x, w) ∈ R₁_Y`, with probability at least `1 − ε` over `r₁`:
   (a) `(f(x; r₁), g(x, w; r₁)) ∈ R₂_Y`, and
   (b) for every `w'` with `(f(x; r₁), w') ∈ R₂_N`, `Pr_{r₂}[(x, h(x, w'; r₁, r₂)) ∈ R₁_N] ≥ 1 − ε`;
2. for every `x ∈ N₁`, `Pr_{r₁}[f(x; r₁) ∈ N₂] ≥ 1 − ε`.

**Formalization Note** As in `RandHalfLevin`, condition 1 is read for every `(x, w) ∈ R₁_Y`. `h` is timed
on the arguments of condition 1(b). -/
def RandLevin (P : WRel Samp Wit) (t : ℕ → ℕ) (ε : ℝ) (ρ ρ₂ : ℕ → ℕ)
    (f : List Bool → List Bool → Samp) (g : List Bool → List Bool → List Bool → Wit)
    (h : List Bool → Wit → List Bool → List Bool → List Bool) : Prop :=
  TimeOn (ι := {i : List Bool × List Bool // i.2.length = ρ i.1.length})
    (fun i => [i.1.1, i.1.2]) (fun i => (f i.1.1 i.1.2).2.code) (fun i => t i.1.1.length) ∧
  TimeOn (ι := {i : List Bool × List Bool × List Bool //
      SATRel.RY i.1 i.2.1 ∧ i.2.2.length = ρ i.1.length})
    (fun i => [i.1.1, i.1.2.1, i.1.2.2]) (fun i => circCode (g i.1.1 i.1.2.1 i.1.2.2).2)
    (fun i => t i.1.1.length) ∧
  TimeOn (ι := {i : List Bool × Wit × List Bool × List Bool //
      i.2.2.1.length = ρ i.1.length ∧ i.2.2.2.length = ρ₂ i.1.length ∧
      P.RN (f i.1 i.2.2.1) i.2.1})
    (fun i => [i.1.1, circCode i.1.2.1.2, i.1.2.2.1, i.1.2.2.2])
    (fun i => h i.1.1 i.1.2.1 i.1.2.2.1 i.1.2.2.2) (fun i => t i.1.1.length) ∧
  (∀ x w, SATRel.RY x w → 1 - ε ≤ coinAvg (ρ x.length)
    (fun r => if P.RY (f x (bits r)) (g x w (bits r)) ∧
        ∀ w', P.RN (f x (bits r)) w' → 1 - ε ≤ coinAvg (ρ₂ x.length)
          (fun r₂ => if SATRel.RN x (h x w' (bits r) (bits r₂)) then 1 else 0)
      then 1 else 0)) ∧
  (∀ x ∈ SATRel.No, 1 - ε ≤ coinAvg (ρ x.length)
    (fun r => if f x (bits r) ∈ P.No then 1 else 0))

/-- `f` is **honest** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 5, last paragraph, p.17 (PDF 19)): for some `δ > 0`, for all
`x`, `|f(x)| ≥ |x|^δ`, where `|f(x)|` is the length of the description of the output circuit. -/
def Honest (f : List Bool → Samp) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : List Bool, (x.length : ℝ) ^ δ ≤ ((f x).2.code.length : ℝ)

/-- `(f, g)` are **deterministic polynomial-time machines** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorems 71, 72, 74, p.53 (PDF 55):
"a pair of machines `(f, g)`").

**Formalization Note** Theorems 71, 72 and 74 print no time bound; the machines are polynomial-time in
their input length (Lemma 75 runs `f` inside a polynomial-time `Enc`). They are timed on all inputs, so
that one pair of machines serves every polynomial `G, ε⁻¹`. -/
def UnifPoly (f : List Bool → Samp) (g : List Bool → List Bool → Wit) : Prop :=
  PolyTimeOn (ι := List Bool) (fun x => [x]) (fun x => (f x).2.code) ∧
  PolyTimeOn (ι := List Bool × List Bool) (fun i => [i.1, i.2]) (fun i => circCode (g i.1 i.2).2)

/-- `h(x, w'; r)` is a **randomized polynomial-time machine** with `hc(|x|, |w'|)` coins, polynomially
many (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 72, p.53 (PDF 55): "`h` may be randomized"); `|w'|` is the length of the description
of the circuit `w'`. -/
def RandPolyMachine (h : List Bool → Wit → List Bool → List Bool) (hc : ℕ → ℕ → ℕ) : Prop :=
  (∃ c : ℕ, ∀ a b, hc a b ≤ (a + b + 2) ^ c) ∧
  PolyTimeOn (ι := {i : List Bool × Wit × List Bool //
      i.2.2.length = hc i.1.length (circCode i.2.1.2).length})
    (fun i => [i.1.1, circCode i.1.2.1.2, i.1.2.2]) (fun i => h i.1.1 i.1.2.1 i.1.2.2)

open Classical in
/-- **Randomized witness recovery** with error `ε` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 5, condition 1(b), p.17 (PDF 19)):
for every sufficiently long `x` and every `w'` with `(f(x), w') ∈ R₂_N`, `Pr_r[(x, h(x, w'; r)) ∈ R₁_N] ≥ 1 − ε`.

**Formalization Note** Used inside "for all polynomial `G`, `ε⁻¹`" with `h` fixed beforehand (Theorem 72),
the condition is asymptotic in `|x|`, the threshold depending on `G`, `ε⁻¹`: this is what the proofs of
Lemmas 75 (Item 1) and 76 (Item 1) give, from an extractor that works for all large `n` (see
`ExtractableWE`). -/
def RandRecover (P : WRel Samp Wit) (f : List Bool → Samp)
    (h : List Bool → Wit → List Bool → List Bool) (hc : ℕ → ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ x : List Bool, x.length = n → ∀ w', P.RN (f x) w' →
    1 - ε ≤ coinAvg (hc x.length (circCode w'.2).length)
      (fun r => if SATRel.RN x (h x w' (bits r)) then 1 else 0)

/-- The reduction outputs **instances of polynomial size** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definitions 21, 23, 25, 27, 73,
pp.22–24, 53: "an instance … at input length `n` consists of a poly(n)-size circuit `E`"; Definition 4,
condition 1: "`f` maps instances of the first promise problem to instances of the second"): for one
constant `c`, every output `E = f(x)` has a description of length at most `(n + 2)^c`, `n = E.len` its
input length.

**Formalization Note** The size is the description length `MCircuit.code` (gates, outputs and coin
inputs), polynomially related to the gate count; `n + 2` avoids the zero bound at `n = 0`. -/
def PolySizeOut (f : List Bool → Samp) : Prop :=
  ∃ c : ℕ, ∀ x : List Bool, (f x).2.code.length ≤ ((f x).len + 2) ^ c

/-- `PolySizeOut` for a randomized reduction `f(x; r)` with `ρ(|x|)` coins: every output, for every
choice of coins, is an instance of polynomial size. -/
def RandPolySizeOut (ρ : ℕ → ℕ) (f : List Bool → List Bool → Samp) : Prop :=
  ∃ c : ℕ, ∀ x r : List Bool, r.length = ρ x.length →
    (f x r).2.code.length ≤ ((f x r).len + 2) ^ c

end ProofCryptoSynergy.Supplement


