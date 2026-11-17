-- Prove2me | Definitions.Def_SingleInteraction_Supplement_Variants
-- name    : SingleInteraction_Supplement_Variants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:03:45.561983+00:00
-- url     : https://prove2.me/theorems/c7f2d0fa-ebc8-4c55-a618-f70abc51b4f8
-- title:
--   Geometrically local, precise, frustration-free and guided single-interaction problems
-- statement:
--   Variants of SIH$_k$ for a fixed $k$-qubit interaction $h$ (or a family $h^{(n)}$), with $H=\sum_{e\in L}h_e$ over pairwise distinct ordered $k$-tuples of distinct qubits.
--
--   1. **Geometric restriction** (Definition 19, $D=2$). The instance comes with an injective placement of its qubits in $\mathbb Z^2$. For constants $\Delta,R$, it is admissible when every qubit lies in at most $\Delta$ tuples and any two qubits of a common tuple are at lattice ($\ell^1$) distance at most $R$. The promise is that of SIH$_k$ (or DSIH$_k$) on admissible instances.
--   2. **Precise-SIH$_k$** (Definition 40): as SIH$_k$, with the promise gap $b-a\ge2^{-p(n)}$ in place of $b-a\ge1/\mathrm{poly}(n)$.
--   3. **FF-SIH$_k$** (Definition 39): input $(n,L,b)$ with $b\ge1/\mathrm{poly}(n)$; YES: $\lambda_{\min}(H)=0$; NO: $\lambda_{\min}(H)\ge b$.
--   4. **Guided-SIH$_k$** (Definitions 13, 41): an SIH$_k$ instance with $b-a\ge1/\mathrm{poly}(n)$, a nonempty set $S\subseteq\{0,1\}^n$ of polynomial size defining the semi-classical state $|u\rangle=|S|^{-1/2}\sum_{x\in S}|x\rangle$, and $\delta\in(0,1]$ with $\delta\ge1/\mathrm{poly}(n)$; the promise is $\|\Pi_H|u\rangle\|\ge\delta$, with $\Pi_H$ the projector onto the ground space, and $\lambda_{\min}(H)\le a$ (YES) or $\lambda_{\min}(H)\ge b$ (NO). A further restriction (Theorem 82) asks for a one-dimensional ground space, a spectral gap $\ge1/(n+1)^{p_{\mathrm{gap}}}$ and a normalized ground state $\phi$ with $|\langle u|\phi\rangle|\ge1-1/(n+1)^q$.
--
--   These are the problems of Theorems 65, 77, 80, 81 and 82.
--
--   **Formalization Note** The lattice placement is part of the instance (a reading: a hardness reduction must output it, as the paper's do). Every "poly" is the instance exponent $c$: bit lengths at most $(n+1)^c$, gaps $\ge1/(n+1)^c$ or $\ge2^{-(n+1)^c}$, $|S|\le(n+1)^c$. Bit $j$ of a string of $S$ is qubit $j$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 19, p.22; Definitions 39–41, pp.32–33; Definition 13, pp.19–20

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_SIHInstance_Valid
import Definitions.Def_SingleInteraction_tupleTerm
import Definitions.Def_SingleInteraction_sihHam
import Definitions.Def_SingleInteraction_hamPromise
import Definitions.Def_SingleInteraction_Supplement_Linalg

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-!
# Geometric, precise, frustration-free and guided single-interaction problems

Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version,
sha256 19ddc444…): Definition 19 (geometrically local hypergraph, p.22) with `D = 2`, used in
Theorems 65, 77, 81; Definition 39 (FF-SIH_k, p.32); Definition 40 (Precise-SIH_k, p.32);
Definitions 13 (semi-classical state, pp.19–20) and 41 (Guided-SIH_k, p.33).

**Formalization Note**
* Geometric restriction. An instance carries an embedding `ι : {0, …, n−1} → ℤ²`, the list of the
  lattice positions of the qubits, which must be injective (a reading: the embedding is part of the
  instance, so a hardness reduction must output it). For constants `Δ, R`, a valid embedded instance
  has every qubit in at most `Δ` tuples (bounded degree) and every two qubits of a common tuple at
  `ℓ¹` lattice distance at most `R` (bounded range). "Even when restricted to …" is: for some `Δ, R`
  fixed before the instance, the restricted problem is complete. Any fixed norm on `ℤ²` gives the same
  notion, as `R` is existential.
* `TuplesValid k x` is the tuple clause of the base `SIHInstance.Valid` (length `k`, entries
  `< n`, distinct entries, pairwise distinct tuples), restated so that the precise and FF variants can
  replace the threshold clause.
* Precise-SIH_k: the thresholds have at most `(n+1)^c` bits and `b − a ≥ 2^{−(n+1)^c}`.
* FF-SIH_k: the input is `(n, L, b)`; `b` has at most `(n+1)^c` bits and `b ≥ 1/(n+1)^c`; YES is
  `λmin(H) = 0` exactly, NO is `λmin(H) ≥ b`.
* Guided-SIH_k: an `SIH_k` instance valid at exponent `c` (so `b − a ≥ 1/(n+1)^c`), a nonempty
  list `S` of distinct `n`-bit strings with `|S| ≤ (n+1)^c` (bit `j` of a string is qubit `j`), and
  `δ ∈ (0, 1]` with at most `(n+1)^c` bits and `δ ≥ 1/(n+1)^c`. `|u⟩ = |S|^{−1/2} Σ_{x∈S} |x⟩`;
  the promise is `‖Π_H |u⟩‖ ≥ δ` together with `λmin(H) ≤ a` (YES) or `λmin(H) ≥ b` (NO), where
  `Π_H` is the orthogonal projector onto the ground space. -/

/-- The tuple clause of `SIHInstance.Valid`. -/
def TuplesValid (k n : ℕ) (tuples : List (List ℕ)) : Prop :=
  (∀ l ∈ tuples, l.length = k ∧ (∀ v ∈ l, v < n) ∧ l.Nodup) ∧ tuples.Nodup

/-- `H = Σ_{e∈L} h_e` for a raw tuple list. -/
noncomputable def tupleHam (n k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (tuples : List (List ℕ)) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (tuples.map (tupleTerm n k h)).sum

/-! ## Geometric locality -/

/-- An `SIH`/`DSIH` instance with lattice positions of its qubits. -/
structure GeoInstance where
  base : SIHInstance
  pos : List (ℤ × ℤ)

/-- Equivalence used to build the code. -/
def geoInstanceEquiv : GeoInstance ≃ SIHInstance × List (ℤ × ℤ) where
  toFun x := (x.base, x.pos)
  invFun y := ⟨y.1, y.2⟩
  left_inv x := by cases x; rfl
  right_inv y := by rcases y with ⟨a, b⟩; rfl

/-- The code of an embedded instance. -/
def geoCodec : Codec GeoInstance :=
  BinaryEncoding.equiv (pair sihCodec (BinaryEncoding.list (pair integer integer))) geoInstanceEquiv

/-- `ℓ¹` distance on `ℤ²`. -/
def dist1 (p q : ℤ × ℤ) : ℕ := (p.1 - q.1).natAbs + (p.2 - q.2).natAbs

/-- The `(Δ, R)` geometric restriction (Definition 19 with `D = 2`). -/
def GeoValid (Δ R : ℕ) (x : GeoInstance) : Prop :=
  x.pos.length = x.base.n ∧ x.pos.Nodup ∧
    (∀ v : ℕ, v < x.base.n → (x.base.tuples.filter (fun l => decide (v ∈ l))).length ≤ Δ) ∧
    ∀ l ∈ x.base.tuples, ∀ u ∈ l, ∀ v ∈ l, dist1 (x.pos.getD u (0, 0)) (x.pos.getD v (0, 0)) ≤ R

/-- Geometrically local `SIH_k` with fixed interaction `h`. -/
noncomputable def geoSihProblem (k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (Δ R c : ℕ) : PromiseProblem GeoInstance :=
  hamPromise (fun x => x.base.Valid k c ∧ GeoValid Δ R x) (fun x => x.base.n)
    (fun x => sihHam k h x.base) (fun x => (x.base.a.value : ℝ)) (fun x => (x.base.b.value : ℝ))
    (fun _ hx => hx.1.2.2.lt)

/-- Geometrically local `DSIH_k` with family `h^(n)`. -/
noncomputable def geoDsihProblem (k : ℕ) (hfam : ℕ → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (Δ R c : ℕ) : PromiseProblem GeoInstance :=
  hamPromise (fun x => x.base.Valid k c ∧ GeoValid Δ R x) (fun x => x.base.n)
    (fun x => sihHam k (hfam x.base.n) x.base) (fun x => (x.base.a.value : ℝ))
    (fun x => (x.base.b.value : ℝ)) (fun _ hx => hx.1.2.2.lt)

/-! ## Precise thresholds -/

/-- Precise-SIH validity (Definition 40): tuples as in `SIH_k`, thresholds of at most `(n+1)^c`
bits with `b − a ≥ 2^{−(n+1)^c}`. -/
def PreciseValid (k c : ℕ) (x : SIHInstance) : Prop :=
  TuplesValid k x.n x.tuples ∧ 0 < x.a.denominator ∧ 0 < x.b.denominator ∧
    (binaryRationalCodec.encode x.a).length ≤ (x.n + 1) ^ c ∧
    (binaryRationalCodec.encode x.b).length ≤ (x.n + 1) ^ c ∧
    (1 / 2 : ℝ) ^ ((x.n + 1) ^ c) ≤ (x.b.value : ℝ) - (x.a.value : ℝ)

theorem PreciseValid.lt {k c : ℕ} {x : SIHInstance} (hx : PreciseValid k c x) :
    (x.a.value : ℝ) < (x.b.value : ℝ) := by
  have : (0 : ℝ) < (1 / 2 : ℝ) ^ ((x.n + 1) ^ c) := by positivity
  linarith [hx.2.2.2.2.2]

/-- Geometrically local Precise-SIH_k with fixed interaction `h`. -/
noncomputable def geoPreciseSihProblem (k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (Δ R c : ℕ) : PromiseProblem GeoInstance :=
  hamPromise (fun x => PreciseValid k c x.base ∧ GeoValid Δ R x) (fun x => x.base.n)
    (fun x => sihHam k h x.base) (fun x => (x.base.a.value : ℝ)) (fun x => (x.base.b.value : ℝ))
    (fun _ hx => hx.1.lt)

/-! ## Frustration-free -/

/-- An FF-SIH instance `(n, L, b)`. -/
structure FFInstance where
  n : ℕ
  tuples : List (List ℕ)
  b : BinaryRational

/-- Equivalence used to build the code. -/
def ffInstanceEquiv : FFInstance ≃ ℕ × (List (List ℕ) × BinaryRational) where
  toFun x := (x.n, x.tuples, x.b)
  invFun y := ⟨y.1, y.2.1, y.2.2⟩
  left_inv x := by cases x; rfl
  right_inv y := by rcases y with ⟨a, b, c⟩; rfl

/-- The code of an FF instance (`n` in unary). -/
def ffCodec : Codec FFInstance :=
  BinaryEncoding.equiv (pair unary (pair (BinaryEncoding.list (BinaryEncoding.list natural))
    binaryRationalCodec)) ffInstanceEquiv

/-- FF-SIH validity (Definition 39). -/
def FFInstance.Valid (k c : ℕ) (x : FFInstance) : Prop :=
  TuplesValid k x.n x.tuples ∧ 0 < x.b.denominator ∧
    (binaryRationalCodec.encode x.b).length ≤ (x.n + 1) ^ c ∧
    (((x.n : ℝ) + 1) ^ c)⁻¹ ≤ (x.b.value : ℝ)

/-- FF-SIH_k with fixed interaction `h` (Definition 39): YES `λmin(H) = 0`, NO `λmin(H) ≥ b`. -/
noncomputable def ffSihProblem (k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) (c : ℕ) :
    PromiseProblem FFInstance where
  yes := {x | x.Valid k c ∧ lamMin (tupleHam x.n k h x.tuples) = 0}
  no := {x | x.Valid k c ∧ (x.b.value : ℝ) ≤ lamMin (tupleHam x.n k h x.tuples)}
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨hv, h0⟩ ⟨-, hb⟩
    have : (0 : ℝ) < (((x.n : ℝ) + 1) ^ c)⁻¹ := by positivity
    linarith [hv.2.2.2]

/-! ## Guided -/

/-- A Guided-SIH instance: an `SIH` instance, the list `S` of basis strings of the semi-classical
guiding state, and the overlap bound `δ`. -/
structure GuidedInstance where
  base : SIHInstance
  S : List (List Bool)
  δ : BinaryRational

/-- Equivalence used to build the code. -/
def guidedInstanceEquiv : GuidedInstance ≃ SIHInstance × (List (List Bool) × BinaryRational) where
  toFun x := (x.base, x.S, x.δ)
  invFun y := ⟨y.1, y.2.1, y.2.2⟩
  left_inv x := by cases x; rfl
  right_inv y := by rcases y with ⟨a, b, c⟩; rfl

/-- A length-prefixed code for a bit string (the length, then the bits verbatim). -/
def bitsListCodec : Codec (List Bool) where
  encode w := natural.encode w.length ++ w
  read s := let (n, t) := natural.read s; (t.take n, t.drop n)
  read_encode w tail := by
    simp only [List.append_assoc, natural.read_encode, List.take_left', List.drop_left']

/-- The code of a guided instance (each string of `S` as a list of bits). -/
def guidedCodec : Codec GuidedInstance :=
  BinaryEncoding.equiv (pair sihCodec (pair
    (BinaryEncoding.list bitsListCodec) binaryRationalCodec)) guidedInstanceEquiv

/-- The `n`-bit string of a basis state (bit `j` is qubit `j`). -/
def basisBits {n : ℕ} (s : Fin n → Fin 2) : List Bool :=
  List.ofFn fun j => decide (s j = 1)

/-- The semi-classical state `|u⟩ = |S|^{−1/2} Σ_{x∈S} |x⟩` (Definition 13). -/
noncomputable def semiClassical (n : ℕ) (S : List (List Bool)) : EuclideanSpace ℂ (Fin n → Fin 2) :=
  ∑ s : Fin n → Fin 2,
    if basisBits s ∈ S then ((Real.sqrt S.length : ℂ)⁻¹) • EuclideanSpace.single s 1 else 0

/-- Guided-SIH validity (Definition 41) at exponent `c`. -/
def GuidedInstance.Valid (k c : ℕ) (x : GuidedInstance) : Prop :=
  x.base.Valid k c ∧ x.S ≠ [] ∧ x.S.Nodup ∧ (∀ w ∈ x.S, w.length = x.base.n) ∧
    x.S.length ≤ (x.base.n + 1) ^ c ∧ 0 < x.δ.denominator ∧
    (binaryRationalCodec.encode x.δ).length ≤ (x.base.n + 1) ^ c ∧
    (((x.base.n : ℝ) + 1) ^ c)⁻¹ ≤ (x.δ.value : ℝ) ∧ (x.δ.value : ℝ) ≤ 1

/-- `‖Π_H |u⟩‖` for the guiding state of `x`. -/
noncomputable def GuidedInstance.overlap (k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (x : GuidedInstance) : ℝ :=
  ‖(groundSpace (sihHam k h x.base)).starProjection (semiClassical x.base.n x.S)‖

/-- Guided-SIH_k with fixed interaction `h`, restricted by an extra condition `Extra` on instances
(`Extra = fun _ => True` is Definition 41 itself). -/
noncomputable def guidedSihProblemOn (k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (c : ℕ) (Extra : GuidedInstance → Prop) : PromiseProblem GuidedInstance where
  yes := {x | x.Valid k c ∧ Extra x ∧ (x.δ.value : ℝ) ≤ x.overlap k h ∧
    lamMin (sihHam k h x.base) ≤ (x.base.a.value : ℝ)}
  no := {x | x.Valid k c ∧ Extra x ∧ (x.δ.value : ℝ) ≤ x.overlap k h ∧
    (x.base.b.value : ℝ) ≤ lamMin (sihHam k h x.base)}
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨hv, -, -, hle⟩ ⟨-, -, -, hge⟩
    exact absurd (hge.trans hle) (not_le.mpr hv.1.2.2.lt)

/-- Guided-SIH_k (Definition 41). -/
noncomputable def guidedSihProblem (k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (c : ℕ) : PromiseProblem GuidedInstance :=
  guidedSihProblemOn k h c (fun _ => True)

/-- The restriction of Theorem 82's "Moreover": a unique ground state, spectral gap at least
`1/(n+1)^pg`, and a normalized ground state `ϕ` with `|⟨u|ϕ⟩| ≥ 1 − 1/(n+1)^q`. -/
def GuidedInstance.WellGuided (k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (pg q : ℕ) (x : GuidedInstance) : Prop :=
  Module.finrank ℂ (groundSpace (sihHam k h x.base)) = 1 ∧
    (excited (sihHam k h x.base)).Nonempty ∧
    (((x.base.n : ℝ) + 1) ^ pg)⁻¹ ≤ specGap (sihHam k h x.base) ∧
    ∃ φ ∈ groundSpace (sihHam k h x.base), ‖φ‖ = 1 ∧
      1 - (((x.base.n : ℝ) + 1) ^ q)⁻¹ ≤ ‖inner ℂ (semiClassical x.base.n x.S) φ‖

end Supplement

end SingleInteraction


